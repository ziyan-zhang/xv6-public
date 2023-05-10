// File system implementation.  Five layers:
//   + Blocks: allocator for raw disk blocks.
//   + Log: crash recovery for multi-step updates.
//   + Files: inode allocator, reading, writing, metadata.
//   + Directories: inode with special contents (list of other inodes!)
//   + Names: paths like /usr/rtm/xv6/fs.c for convenient naming.
//
// This file contains the low-level file system manipulation
// routines.  The (higher-level) system call implementations
// are in sysfile.c.

#include "types.h"
#include "defs.h"
#include "param.h"
#include "stat.h"
#include "mmu.h"
#include "proc.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "fs.h"
#include "buf.h"
#include "file.h"

#define min(a, b) ((a) < (b) ? (a) : (b))
static void itrunc(struct inode*);
// there should be one superblock per disk device, but we run with
// only one device
struct superblock sb; 

// Read the super block.
void
readsb(int dev, struct superblock *sb)
{
  struct buf *bp;

  bp = bread(dev, 1);
  memmove(sb, bp->data, sizeof(*sb));
  brelse(bp);
}

// Zero a block.  其实块的bitmap置零之后，这个块就可以被分配了，这里将块清零是为了防止块中的数据泄露？
static void
bzero(int dev, int bno)
{
  struct buf *bp;

  bp = bread(dev, bno);
  memset(bp->data, 0, BSIZE);
  log_write(bp);  // log_write的应用1：将该块清零后写回磁盘，这是元数据log。log_write应该出现在transaction中
  brelse(bp);
}

// Blocks.

// Allocate a zeroed disk block.
static uint
balloc(uint dev)
{
  int b, bi, m;
  struct buf *bp;

  bp = 0;
  for(b = 0; b < sb.size; b += BPB){  // BPB: 一个块有多少个bit，这里是一个块一个块的遍历
    bp = bread(dev, BBLOCK(b, sb)); // BBLOCK(b, sb)是第b块的free map的块的地址，将该块读出到bp
    for(bi = 0; bi < BPB && b + bi < sb.size; bi++){  // 遍历该块的每一个bit
      m = 1 << (bi % 8);
      if((bp->data[bi/8] & m) == 0){  // Is block free?
        bp->data[bi/8] |= m;  // Mark block in use.
        log_write(bp);  // log_write的应用2：分配快时，将该块的free map的块写回磁盘，这是元数据log
        brelse(bp);
        bzero(dev, b + bi); // b+bi是第b+bi块，将该块清零
        return b + bi;
      }
    }
    brelse(bp);
  }
  panic("balloc: out of blocks");
}

// Free a disk block.
// 这里包含log_write操作，所以bfree应该是包含在某个transaction中的，该tx里面可能有其他的log_write操作
static void
bfree(int dev, uint b)
{
  struct buf *bp;
  int bi, m;

  // #define BBLOCK(b, sb) (b/BPB + sb.bmapstart)，是第b块的free map的块的地址
  bp = bread(dev, BBLOCK(b, sb)); // 读取第b块的free map的块
  bi = b % BPB; // bi: 块bp的第几个bit表示块b分配与否，BPB是BLOCKSIZE*8=4096*8=32768
  m = 1 << (bi % 8);  // 先算出bi落在块bp的第几个字节
  if((bp->data[bi/8] & m) == 0)
    panic("freeing free block");
  bp->data[bi/8] &= ~m; // 只将该块b对应的位清零，其他位不变
  log_write(bp);  // 对bp->data的修改通过log_write，而不是bwrite写入磁盘，以实现块写入的log absorbion
  brelse(bp);
}

// Inodes.
//
// An inode describes a single unnamed file.
// The inode disk structure holds metadata: the file's type,
// its size, the number of links referring to it, and the
// list of blocks holding the file's content.
//
// The inodes are laid out sequentially on disk at
// sb.startinode. Each inode has a number, indicating its
// position on the disk.
//
// The kernel keeps a cache of in-use inodes in memory
// to provide a place for synchronizing access
// to inodes used by multiple processes. The cached
// inodes include book-keeping information that is
// not stored on disk: ip->ref and ip->valid.
//
// An inode and its in-memory representation go through a
// sequence of states before they can be used by the
// rest of the file system code.
//
// * Allocation: an inode is allocated if its type (on disk)
//   is non-zero. ialloc() allocates, and iput() frees if
//   the reference and link counts have fallen to zero.
//
// * Referencing in cache: an entry in the inode cache
//   is free if ip->ref is zero. Otherwise ip->ref tracks
//   the number of in-memory pointers to the entry (open
//   files and current directories). iget() finds or
//   creates a cache entry and increments its ref; iput()
//   decrements ref.
//
// * Valid: the information (type, size, &c) in an inode
//   cache entry is only correct when ip->valid is 1.
//   ilock() reads the inode from
//   the disk and sets ip->valid, while iput() clears
//   ip->valid if ip->ref has fallen to zero.
//
// * Locked: file system code may only examine and modify
//   the information in an inode and its content if it
//   has first locked the inode.
//
// Thus a typical sequence is:
//   ip = iget(dev, inum)
//   ilock(ip)
//   ... examine and modify ip->xxx ...
//   iunlock(ip)
//   iput(ip)
//
// ilock() is separate from iget() so that system calls can
// get a long-term reference to an inode (as for an open file)
// and only lock it for short periods (e.g., in read()).
// The separation also helps avoid deadlock and races during
// pathname lookup. iget() increments ip->ref so that the inode
// stays cached and pointers to it remain valid.
//
// Many internal file system functions expect the caller to
// have locked the inodes involved; this lets callers create
// multi-step atomic operations.
//
// The icache.lock spin-lock protects the allocation of icache
// entries. Since ip->ref indicates whether an entry is free,
// and ip->dev and ip->inum indicate which i-node an entry
// holds, one must hold icache.lock while using any of those fields.
//
// An ip->lock sleep-lock protects all ip-> fields other than ref,
// dev, and inum.  One must hold ip->lock in order to
// read or write that inode's ip->valid, ip->size, ip->type, &c.

struct {
  struct spinlock lock;
  struct inode inode[NINODE];
} icache;

void
iinit(int dev)  // 初始化保护iNode分配有关的iNode属性的icache.lock和保护iNode其他属性的各个iNode.lock
{
  int i = 0;
  
  initlock(&icache.lock, "icache");
  for(i = 0; i < NINODE; i++) {
    initsleeplock(&icache.inode[i].lock, "inode");
  }

  readsb(dev, &sb);
  cprintf("sb: size %d nblocks %d ninodes %d nlog %d logstart %d\
 inodestart %d bmap start %d\n", sb.size, sb.nblocks,
          sb.ninodes, sb.nlog, sb.logstart, sb.inodestart,
          sb.bmapstart);  // sb.nlog log块数
}

static struct inode* iget(uint dev, uint inum);

//PAGEBREAK!
// Allocate an inode on device dev.
// Mark it as allocated by  giving it type type.
// Returns an unlocked but allocated and referenced inode.
struct inode*
ialloc(uint dev, short type)
{
  int inum;
  struct buf *bp;
  struct dinode *dip;

  for(inum = 1; inum < sb.ninodes; inum++){
    bp = bread(dev, IBLOCK(inum, sb));  // 读取inum对应的块
    dip = (struct dinode*)bp->data + inum%IPB;  // 读取inum对应的inode
    if(dip->type == 0){  // a free inode
      memset(dip, 0, sizeof(*dip));
      dip->type = type; // 改了这个dip->type就表示该iNode已经分配了
      log_write(bp);   // mark it allocated on the disk
      brelse(bp);
      return iget(dev, inum);
    }
    brelse(bp);
  }
  panic("ialloc: no inodes");
}

// 将修改后的内存inode复制到磁盘。必须在每次修改磁盘上的ip->xxx字段之后调用，因为i-node缓存是写通（write-through）的。
// 调用者必须持有ip->lock。
// 可以看到这里的inode写用了log_write，说明inode的更改是通过日志实现的。
void
iupdate(struct inode *ip)
{
  struct buf *bp;
  struct dinode *dip;

  bp = bread(ip->dev, IBLOCK(ip->inum, sb));
  dip = (struct dinode*)bp->data + ip->inum%IPB;  // 这里的+是智能地按照数组的方式移动指针
  dip->type = ip->type; // 将inode的type,major, minor, nlink, size, addrs等属性写到磁盘中
  dip->major = ip->major;
  dip->minor = ip->minor;
  dip->nlink = ip->nlink;
  dip->size = ip->size;
  memmove(dip->addrs, ip->addrs, sizeof(ip->addrs));
  log_write(bp);  // Inode在某个block中，将该block的内存更新写到磁盘上
  brelse(bp);
}

// Find the inode with number inum on device dev
// and return the in-memory copy. Does not lock
// the inode and does not read it from disk.
static struct inode*
iget(uint dev, uint inum)
{
  struct inode *ip, *empty;

  acquire(&icache.lock);

  // Is the inode already cached?
  empty = 0;
  for(ip = &icache.inode[0]; ip < &icache.inode[NINODE]; ip++){
    if(ip->ref > 0 && ip->dev == dev && ip->inum == inum){
      ip->ref++;
      release(&icache.lock);
      return ip;
    }
    if(empty == 0 && ip->ref == 0)    // Remember empty slot.
      empty = ip; // 将该空的iNode指针交给empty.如果最后返回了，empty是最后遍历到的空iNode（不管提前返回与否）
  }

  // Recycle an inode cache entry.
  if(empty == 0)  // 没有因找到内存版iNode提前返回，也没有找到空的iNode给empty，这下就出问题了
    panic("iget: no inodes");

  // 这个时候empty指向的是最后一个iNode，这个iNode的ref==0，所以可以用来存放新的iNode
  ip = empty;
  ip->dev = dev;
  ip->inum = inum;
  ip->ref = 1;  // 为什么这里要设置为1？因为这个iNode是新的，所以只有一个引用
  ip->valid = 0;  // 为什么这里要设置为0？因为这个iNode是新的，所以还没有从磁盘读取过
  release(&icache.lock);

  return ip;
}

// 为ip增加引用计数
// Returns ip to enable ip = idup(ip1) idiom.
struct inode*
idup(struct inode *ip)
{
  acquire(&icache.lock);
  ip->ref++;
  release(&icache.lock);
  return ip;
}

// Lock the given inode.
// Reads the inode from disk if necessary.
void
ilock(struct inode *ip)
{
  struct buf *bp;
  struct dinode *dip;

  if(ip == 0 || ip->ref < 1)  // 合法的iNode地址不能为0；同时要锁定该iNode，其引用计数必须大于0
    panic("ilock");

  acquiresleep(&ip->lock);

  if(ip->valid == 0){ // ip->valid==0，表明该iNode只是分配了，还没有从磁盘读取过
    bp = bread(ip->dev, IBLOCK(ip->inum, sb));
    dip = (struct dinode*)bp->data + ip->inum%IPB;  // IPB表示一个块中有多少个iNode。
    ip->type = dip->type;
    ip->major = dip->major;
    ip->minor = dip->minor;
    ip->nlink = dip->nlink;
    ip->size = dip->size;
    memmove(ip->addrs, dip->addrs, sizeof(ip->addrs));  // 拷贝iNode中指向数据块的指针
    brelse(bp);
    ip->valid = 1;
    if(ip->type == 0)
      panic("ilock: no type");
  }
}

// 解锁给定的iNode
void
iunlock(struct inode *ip)
{
  if(ip == 0 || !holdingsleep(&ip->lock) || ip->ref < 1)  // 空指针、没有持有锁、引用计数小于1，都是不合法的
    panic("iunlock");

  releasesleep(&ip->lock);
}

// 降低内存中的inode的引用计数。
// 如果那是最后一个引用，inode缓存条目可以回收。
// 如果那是最后一个引用，而且inode没有链接到它，就释放磁盘上的inode（和它的内容）。
// 所有对iput()的调用都必须在事务中，以防它必须释放inode。
void
iput(struct inode *ip)
{
  acquiresleep(&ip->lock);
  if(ip->valid && ip->nlink == 0){
    acquire(&icache.lock);  // icache 是 iNode cache，保护的是各个描述 iNode 的数据，比如引用计数
    int r = ip->ref;  // 这里应该是因为 ip->ref 会被分配 iNode 等其他进程用到，所以单独一个锁，不放在 iNode 锁里面
    // 因为其他并发进行的操作（如扫描 icache 找空闲 iNode）也要用到 iNode 锁，就导致锁了太长时间 iNode。
    release(&icache.lock);
    if(r == 1){
      // inode has no links and no other references: truncate and free.
      itrunc(ip);
      ip->type = 0;
      iupdate(ip);
      ip->valid = 0;
    }
  }
  releasesleep(&ip->lock);

  acquire(&icache.lock);  // 如前，这里用 icache 的锁来保护 iNode 的引用计数
  ip->ref--;
  release(&icache.lock);
}

// Common idiom: unlock, then put.
void
iunlockput(struct inode *ip)
{
  iunlock(ip);
  iput(ip);
}

//PAGEBREAK!
// Inode content
//
// The content (data) associated with each inode is stored
// in blocks on the disk. The first NDIRECT block numbers
// are listed in ip->addrs[].  The next NINDIRECT blocks are
// listed in block ip->addrs[NDIRECT].

// Return the disk block address of the nth block in inode ip.
// If there is no such block, bmap allocates one.
static uint
bmap(struct inode *ip, uint bn)
{
  uint addr, *a;
  struct buf *bp;

  if(bn < NDIRECT){
    if((addr = ip->addrs[bn]) == 0)
      ip->addrs[bn] = addr = balloc(ip->dev);
    return addr;
  }
  bn -= NDIRECT;

  if(bn < NINDIRECT){
    // Load indirect block, allocating if necessary.
    if((addr = ip->addrs[NDIRECT]) == 0)  // 第NDIRECT个块刚好要用间接块存，之前没有分配间接块
      ip->addrs[NDIRECT] = addr = balloc(ip->dev);
    bp = bread(ip->dev, addr);
    a = (uint*)bp->data;
    if((addr = a[bn]) == 0){
      a[bn] = addr = balloc(ip->dev); // 不管是新分配的间接块还是原来的间接块，直接块未必分配了
      log_write(bp);
    }
    brelse(bp);
    return addr;
  }

  panic("bmap: out of range");
}

// 下面两种情形都满足的时候，截断iNode：没有目录项指向它，没有进程打开它
// Truncate inode (discard contents).
// Only called when the inode has no links
// to it (no directory entries referring to it)
// and has no in-memory reference to it (is
// not an open file or current directory).
static void
itrunc(struct inode *ip)
{
  int i, j;
  struct buf *bp;
  uint *a;

  for(i = 0; i < NDIRECT; i++){
    if(ip->addrs[i]){
      bfree(ip->dev, ip->addrs[i]); // free直接块指针指向的块
      ip->addrs[i] = 0; // free直接块指针
    }
  }

  if(ip->addrs[NDIRECT]){
    bp = bread(ip->dev, ip->addrs[NDIRECT]);
    a = (uint*)bp->data;
    for(j = 0; j < NINDIRECT; j++){
      if(a[j])
        bfree(ip->dev, a[j]);
    }
    brelse(bp);
    bfree(ip->dev, ip->addrs[NDIRECT]); // free间接块指针指向的块
    ip->addrs[NDIRECT] = 0; // free间接块指针
  }

  ip->size = 0;
  iupdate(ip);
}

// Copy stat information from inode.
// Caller must hold ip->lock.
void
stati(struct inode *ip, struct stat *st)
{
  st->dev = ip->dev;
  st->ino = ip->inum;
  st->type = ip->type;
  st->nlink = ip->nlink;
  st->size = ip->size;
}

//PAGEBREAK!
// Read data from inode.
// Caller must hold ip->lock.
int
readi(struct inode *ip, char *dst, uint off, uint n)
{
  uint tot, m;
  struct buf *bp;

  if(ip->type == T_DEV){  // T_DEV 3, 表示设备文件
    if(ip->major < 0 || ip->major >= NDEV || !devsw[ip->major].read)
      return -1;
    return devsw[ip->major].read(ip, dst, n);
  }

  if(off > ip->size || off + n < off) // 等价于n<0?
    return -1;
  if(off + n > ip->size)
    n = ip->size - off;

  for(tot=0; tot<n; tot+=m, off+=m, dst+=m){
    bp = bread(ip->dev, bmap(ip, off/BSIZE)); // 读off所在的块，BSIZE=512
    m = min(n - tot, BSIZE - off%BSIZE);  // n-tot是剩余未拷贝的字节数；BSIZE-off%BSIZE是当前块剩余的字节数
    memmove(dst, bp->data + off%BSIZE, m);  // off%BSIZE是当前块的拷贝起始偏移量。读就是从磁盘buffer拷贝到内存dst
    brelse(bp); // 拷贝完之后释放当前块
  }
  return n;
}

// PAGEBREAK!
// Write data to inode.
// Caller must hold ip->lock.
int
writei(struct inode *ip, char *src, uint off, uint n)
{
  uint tot, m;
  struct buf *bp;

  if(ip->type == T_DEV){
    if(ip->major < 0 || ip->major >= NDEV || !devsw[ip->major].write)
      return -1;
    return devsw[ip->major].write(ip, src, n);
  }

  if(off > ip->size || off + n < off)
    return -1;
  if(off + n > MAXFILE*BSIZE) // MAXFILE是一个文件最多可包含的块数，BSIZE是一个块的字节数
    return -1;

  for(tot=0; tot<n; tot+=m, off+=m, src+=m){
    bp = bread(ip->dev, bmap(ip, off/BSIZE));
    m = min(n - tot, BSIZE - off%BSIZE);
    memmove(bp->data + off%BSIZE, src, m);  // 写就是从内存src移动到磁盘buffer中
    log_write(bp);  // 写到磁盘buffer之后，通过log_write写到磁盘中
    brelse(bp);
  }

  if(n > 0 && off > ip->size){
    ip->size = off;
    iupdate(ip);  // 追加了新的块到文件中，更新iNode的size
  }
  return n;
}

//PAGEBREAK!
// Directories

int
namecmp(const char *s, const char *t)
{
  return strncmp(s, t, DIRSIZ);
}

// 在目录中查找目录条目。如果找到，返回该条目对应的文件inode，将*poff设置为条目的字节偏移量。没找到就返回0
struct inode*
dirlookup(struct inode *dp, char *name, uint *poff)
{
  uint off, inum;
  struct dirent de;

  if(dp->type != T_DIR) // T_DIR 1, 表示目录文件
    panic("dirlookup not DIR");

  for(off = 0; off < dp->size; off += sizeof(de)){  // 遍历目录文件中的所有目录条目
    if(readi(dp, (char*)&de, off, sizeof(de)) != sizeof(de))  // ip, dst, off, n
      panic("dirlookup read");
    if(de.inum == 0)  // 读出来一个空的日志条目，直接跳过后面，找下一项
      continue;
    if(namecmp(name, de.name) == 0){
      // entry matches path element
      if(poff)
        *poff = off;
      inum = de.inum;
      return iget(dp->dev, inum);
    }
  }

  return 0; // 找到了就返回inode的指针，没找到就返回0
}

// Write a new directory entry (name, inum) into the directory dp.
// dirlink只负责写inode操作，将name和inum写到dp目录文件中。inode的引用计数增加放到系统调用sys_link中
int
dirlink(struct inode *dp, char *name, uint inum)
{
  int off;
  struct dirent de;
  struct inode *ip;

  // Check that name is not present.
  if((ip = dirlookup(dp, name, 0)) != 0){ // 如果name已经存在，就返回-1
    iput(ip);
    return -1;
  }

  // Look for an empty dirent.
  for(off = 0; off < dp->size; off += sizeof(de)){
    if(readi(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
      panic("dirlink read");
    if(de.inum == 0)
      break;  // 找到了空的目录条目，跳出循环
  }

  strncpy(de.name, name, DIRSIZ);
  de.inum = inum;
  if(writei(dp, (char*)&de, off, sizeof(de)) != sizeof(de))   // ip, src, off, n
    panic("dirlink");

  return 0;
}

//PAGEBREAK!
// Paths

// 将path中的下一个路径元素复制到name中。返回指向复制元素后面的元素的指针新*path。
// 返回的路径没有前导斜杠，所以调用者可以检查*path=='\0'来查看name是否是最后一个元素。
// 如果没有要删除的名称，则返回0。
// Copy the next path element from path into name.
// Return a pointer to the element following the copied one.
// The returned path has no leading slashes,
// so the caller can check *path=='\0' to see if the name is the last one.
// If no name to remove, return 0.
//
// Examples:
//   skipelem("a/bb/c", name) = "bb/c", setting name = "a"
//   skipelem("///a//bb", name) = "bb", setting name = "a"
//   skipelem("a", name) = "", setting name = "a"
//   skipelem("", name) = skipelem("////", name) = 0
//
static char*
skipelem(char *path, char *name)
{
  char *s;
  int len;

  while(*path == '/')
    path++;
  if(*path == 0)
    return 0;
  s = path;
  while(*path != '/' && *path != 0)
    path++;
  len = path - s;
  if(len >= DIRSIZ)
    memmove(name, s, DIRSIZ);
  else {
    memmove(name, s, len);
    name[len] = 0;
  }
  while(*path == '/')   // 跳过多余的斜杠,返回指向复制元素后面的元素的指针
    path++;
  return path;
}

// 查找并返回path name的inode. 如果 parent != 0, 返回父目录的inode并将最后的路径元素复制到name中，name必须有DIRSIZ字节的空间。
// 必须在事务内部调用，因为它调用iput()。
// Look up and return the inode for a path name.
// If parent != 0, return the inode for the parent and copy the final
// path element into name, which must have room for DIRSIZ bytes.
// Must be called inside a transaction since it calls iput().
static struct inode*
namex(char *path, int nameiparent, char *name)
{
  struct inode *ip, *next;

  if(*path == '/')
    ip = iget(ROOTDEV, ROOTINO);  // 绝对路径，从根节点开始找
  else
    ip = idup(myproc()->cwd);   // 相对路径，从当前目录开始找

  while((path = skipelem(path, name)) != 0){// 将path中的下一个路径元素复制到name中。返回指向复制元素后面的元素的指针新*path。
    ilock(ip);
    if(ip->type != T_DIR){  // inode不是目录文件，解锁并put inode，返回0
      iunlockput(ip);
      return 0;
    }
    if(nameiparent && *path == '\0'){
      // Stop one level early.
      iunlock(ip);
      return ip;
    }
    // 在目录中查找目录条目。如果找到，返回该条目对应的文件的inode，将*poff设置为条目的字节偏移量。没找到就返回0.
    if((next = dirlookup(ip, name, 0)) == 0){   // 没找到name对应的inode,解锁并put inode，返回0
      iunlockput(ip);
      return 0;
    }
    iunlockput(ip);
    ip = next;  // 找到了name对应的inode，继续找下一个name对应的inode
  }
  if(nameiparent){
    iput(ip);
    return 0;
  }
  return ip;
}

// 返回路径名中最后一个元素的inode。
struct inode*
namei(char *path)
{
  char name[DIRSIZ];
  return namex(path, 0, name);
}

// 返回路径名中最后一个元素的inode和父目录的inode。
struct inode*
nameiparent(char *path, char *name)
{
  return namex(path, 1, name);
}
