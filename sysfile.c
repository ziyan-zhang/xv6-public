//
// File-system system calls.
// Mostly argument checking, since we don't trust
// user code, and calls into file.c and fs.c.
//

#include "types.h"
#include "defs.h"
#include "param.h"
#include "stat.h"
#include "mmu.h"
#include "proc.h"
#include "fs.h"
#include "spinlock.h"
#include "sleeplock.h"
#include "file.h"
#include "fcntl.h"

// 获取第n个word大小的系统调用参数作为文件描述符，文件描述符存入pfd指向的内存中，struct file指针存入pf指向的内存中
static int
argfd(int n, int *pfd, struct file **pf)
{
  int fd;
  struct file *f;

  if(argint(n, &fd) < 0)  // 从当前进程获取第n个word大小的参数，存入fd指向的内存中。失败返回-1，成功返回0
    return -1;
  if(fd < 0 || fd >= NOFILE || (f=myproc()->ofile[fd]) == 0)  // 检查fd是否合法，以及对应的文件是否存在
    return -1;
  if(pfd) // 如果pfd不为NULL，将fd存入pfd指向的内存中
    *pfd = fd;
  if(pf)  // 如果pf不为NULL，将f存入pf指向的内存中
    *pf = f;
  return 0;
}

// Allocate a file descriptor for the given file.
// Takes over file reference from caller on success.
// 为给定文件f分配一个文件描述符，成功后将文件引用从调用者那里接管;失败返回-1，成功返回文件描述符
static int
fdalloc(struct file *f)
{
  int fd;
  struct proc *curproc = myproc();  // 打开文件表是per-进程的，所以需要获取当前进程

  for(fd = 0; fd < NOFILE; fd++){
    if(curproc->ofile[fd] == 0){
      curproc->ofile[fd] = f;
      return fd;  // 分配成功,返回文件描述符
    }
  }
  return -1;  // 文件描述符未分配成功，返回-1
}

// 获取第0个word大小的系统调用参数作为文件描述符，对应的文件struct file指针存入f指向的内存中
int
sys_dup(void)
{
  struct file *f;
  int fd;

  if(argfd(0, 0, &f) < 0) // 获取第0个word大小的系统调用参数作为文件描述符，文件描述符不存，struct file指针存入f指向的内存中
    return -1;
  if((fd=fdalloc(f)) < 0) // 为上一行得到的文件f分配一个（新的）文件描述符，成功返回文件描述符fd，失败返回-1
    return -1;
  filedup(f);
  return fd;
}

int
sys_read(void)
{
  struct file *f;
  int n;
  char *p;
  // argfd(0,0,&f): 获取第0个word大小的系统调用参数作为文件描述符，struct file指针存入f指向的内存中。作为要读的文件。
  // argint(2, &n): 获取第2个32位系统调用参数，存入n中。作为要读的字节数。
  // argptr(1, &p, n): 获取第1个word大小的系统调用参数，存入p指向的内存中，n是p指向的内存的大小。作为读取的数据存放的地址。
  if(argfd(0, 0, &f) < 0 || argint(2, &n) < 0 || argptr(1, &p, n) < 0)
    return -1;
  // 把文件 *f 读到地址 p 中，从 f_off 位置开始读，n 是读取的字节数
  return fileread(f, p, n);
}

int
sys_write(void)
{
  struct file *f;
  int n;
  char *p;
  // 类似sys_read，第0个参数是文件描述符，第1个参数是要写入的数据的地址，第2个参数是要写入的字节数
  // argint放在前面是因为要先确定第二个参数n，用于验证第三个参数p的合法性
  if(argfd(0, 0, &f) < 0 || argint(2, &n) < 0 || argptr(1, &p, n) < 0)
    return -1;
  return filewrite(f, p, n);
}

int
sys_close(void) // 关闭文件：通过第0个系统调用参数，把文件 *f 关闭，释放文件描述符
{
  int fd;
  struct file *f;

  if(argfd(0, &fd, &f) < 0)
    return -1;
  myproc()->ofile[fd] = 0;
  fileclose(f);
  return 0;
}

// 这里把文件的属性存到了st指向的内存中就结束了，也没有打印啥呀，这有意义吗？
int
sys_fstat(void) // 这里其实终于看出来了，系统调用就是合法性检查加实现具体操作的函数
{
  struct file *f;
  struct stat *st;

  if(argfd(0, 0, &f) < 0 || argptr(1, (void*)&st, sizeof(*st)) < 0)
    return -1;
  return filestat(f, st);
}

// Create the path new as a link to the same inode as old.
// 创建路径new，作为 指向与old索引节点相同 的链接。
// 涉及到inode链接数的增加和目录项的创建，都通过log进行
int
sys_link(void)
{
  char name[DIRSIZ], *new, *old;
  struct inode *dp, *ip;

  if(argstr(0, &old) < 0 || argstr(1, &new) < 0)
    return -1;

  begin_op();
  if((ip = namei(old)) == 0){
    end_op();
    return -1;
  }

  ilock(ip);
  if(ip->type == T_DIR){
    iunlockput(ip);
    end_op();
    return -1;
  }

  ip->nlink++;
  iupdate(ip);
  iunlock(ip);

  if((dp = nameiparent(new, name)) == 0)
    goto bad;
  ilock(dp);
  if(dp->dev != ip->dev || dirlink(dp, name, ip->inum) < 0){
    iunlockput(dp);
    goto bad;
  }
  iunlockput(dp);
  iput(ip);

  end_op();

  return 0;

bad:
  ilock(ip);
  ip->nlink--;
  iupdate(ip);
  iunlockput(ip);
  end_op();
  return -1;
}

// Is the directory dp empty except for "." and ".." ?
static int
isdirempty(struct inode *dp)
{
  int off;
  struct dirent de;

  for(off=2*sizeof(de); off<dp->size; off+=sizeof(de)){
    if(readi(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
      panic("isdirempty: readi");
    if(de.inum != 0)  // inode.num都是初始化为0的，如果不为0，说明有文件
      return 0;
  }
  return 1;
}

//PAGEBREAK!
int
sys_unlink(void)
{
  struct inode *ip, *dp;
  struct dirent de;
  char name[DIRSIZ], *path;
  uint off;

  if(argstr(0, &path) < 0)
    return -1;

  begin_op();
  if((dp = nameiparent(path, name)) == 0){
    end_op();
    return -1;
  }

  ilock(dp);

  // Cannot unlink "." or "..".
  if(namecmp(name, ".") == 0 || namecmp(name, "..") == 0)
    goto bad;

  if((ip = dirlookup(dp, name, &off)) == 0)
    goto bad;
  ilock(ip);

  if(ip->nlink < 1)
    panic("unlink: nlink < 1");
  if(ip->type == T_DIR && !isdirempty(ip)){
    iunlockput(ip);
    goto bad;
  }

  memset(&de, 0, sizeof(de));   // 这里是sys_unlink的实质：把de清零
  if(writei(dp, (char*)&de, off, sizeof(de)) != sizeof(de))
    panic("unlink: writei");
  if(ip->type == T_DIR){
    dp->nlink--;
    iupdate(dp);
  }
  iunlockput(dp);

  ip->nlink--;  // sys_unlink的另一个操作，把ip的nlink减1
  iupdate(ip);
  iunlockput(ip);

  end_op();

  return 0;

bad:
  iunlockput(dp);
  end_op();
  return -1;
}

// 在path指定的目录下创建一个类型为type的文件，设备号为major和minor。
// 文件已存在则返回inode；文件不存在返回新分配inode；失败返回0。
static struct inode*
create(char *path, short type, short major, short minor)
{
  struct inode *ip, *dp;  // ip是新建文件的inode，dp是新建文件的父目录的inode
  char name[DIRSIZ];

  if((dp = nameiparent(path, name)) == 0) // 通过path找到父目录的inode给到dp
    return 0;
  ilock(dp);

  if((ip = dirlookup(dp, name, 0)) != 0){ // 通过父目录的inode dp和文件名name找到了文件的inode ip
    iunlockput(dp);
    ilock(ip);
    if(type == T_FILE && ip->type == T_FILE)
      return ip;  // 如果是创建文件，且文件已经存在，直接返回ip
    iunlockput(ip); // 文件类型不匹配，或者是创建目录，都返回错误0
    return 0;
  }

  if((ip = ialloc(dp->dev, type)) == 0) // 通过父目录的inode dp和文件名name，创建新的inode ip
    panic("create: ialloc");

  ilock(ip);
  ip->major = major;  // 这里是新建文件的inode的初始化
  ip->minor = minor;
  ip->nlink = 1;
  iupdate(ip);

  if(type == T_DIR){  // Create . and .. entries.
    dp->nlink++;  // for ".."
    iupdate(dp);
    // No ip->nlink++ for ".": avoid cyclic ref count.
    if(dirlink(ip, ".", ip->inum) < 0 || dirlink(ip, "..", dp->inum) < 0)
      panic("create dots");
  }

  if(dirlink(dp, name, ip->inum) < 0)
    panic("create: dirlink");

  iunlockput(dp);

  return ip;
}

int
sys_open(void)
{
  char *path;
  int fd, omode;
  struct file *f;
  struct inode *ip;
  // 这里的第一个参数是path，第二个参数是omode
  if(argstr(0, &path) < 0 || argint(1, &omode) < 0)
    return -1;

  begin_op();

  if(omode & O_CREATE){ // 如果sys_open带有创建文件标志
    ip = create(path, T_FILE, 0, 0);  // 如果创建成功，ip指向新建文件的inode
    if(ip == 0){  // 如果新文件创建失败，结束操作并返回-1
      end_op();
      return -1;
    }
  } else {  // 如果sys_open不带有创建文件标志
    if((ip = namei(path)) == 0){  // 通过path找到文件的inode，inode指针给到ip，如果找不到，结束操作并返回-1
      end_op();
      return -1;
    }
    ilock(ip);  // 如果通过path正常找到了文件，锁住inode
    if(ip->type == T_DIR && omode != O_RDONLY){ // 如果是打开目录，但是不是只读模式，结束操作并返回-1
      iunlockput(ip);
      end_op();
      return -1;
    }
  }

  // f为新建的文件结构体，fd为文件描述符
  if((f = filealloc()) == 0 || (fd = fdalloc(f)) < 0){  // file结构或fd至少一个分配失败：
    if(f)
      fileclose(f);
    iunlockput(ip);
    end_op();
    return -1;
  }
  iunlock(ip);
  end_op();

  // 前面inode的操作结束了，因为可能释放inode，所以在log中写。这里之后就是内存中的file操作了。
  f->type = FD_INODE;
  f->ip = ip;
  f->off = 0;
  f->readable = !(omode & O_WRONLY);
  f->writable = (omode & O_WRONLY) || (omode & O_RDWR);
  return fd;
}

// sys_mkdir系统调用调用create函数创建目录，指定type参数为T_DIR
int
sys_mkdir(void)
{
  char *path;
  struct inode *ip;

  begin_op();
  if(argstr(0, &path) < 0 || (ip = create(path, T_DIR, 0, 0)) == 0){
    end_op();
    return -1;
  }
  iunlockput(ip);
  end_op();
  return 0;
}

// 调用create(path, T_DEV, major, minor)创建一个device设备的inode，指定type参数为T_DEV
int
sys_mknod(void)
{
  struct inode *ip;
  char *path;
  int major, minor;

  begin_op();
  if((argstr(0, &path)) < 0 ||
     argint(1, &major) < 0 ||
     argint(2, &minor) < 0 ||
     (ip = create(path, T_DEV, major, minor)) == 0){
    end_op();
    return -1;
  }
  iunlockput(ip);
  end_op();
  return 0;
}

int
sys_chdir(void)
{
  char *path;
  struct inode *ip;
  struct proc *curproc = myproc();
  
  begin_op();
  // 通过第0个次数找到目录path，通过path找到目录的inode，inode指针给到ip，如果找不到，结束操作并返回-1
  if(argstr(0, &path) < 0 || (ip = namei(path)) == 0){
    end_op();
    return -1;
  }
  ilock(ip);
  if(ip->type != T_DIR){  // 如果不是目录，结束操作并返回-1
    iunlockput(ip);
    end_op();
    return -1;
  }
  iunlock(ip);
  iput(curproc->cwd);
  end_op();
  curproc->cwd = ip;
  return 0;
}

int
sys_exec(void)
{
  char *path, *argv[MAXARG];
  int i;
  uint uargv, uarg;

  if(argstr(0, &path) < 0 || argint(1, (int*)&uargv) < 0){
    return -1;
  }
  memset(argv, 0, sizeof(argv));
  for(i=0;; i++){
    if(i >= NELEM(argv))
      return -1;
    if(fetchint(uargv+4*i, (int*)&uarg) < 0)
      return -1;
    if(uarg == 0){
      argv[i] = 0;
      break;
    }
    if(fetchstr(uarg, &argv[i]) < 0)
      return -1;
  }
  return exec(path, argv);
}

int
sys_pipe(void)
{
  int *fd;
  struct file *rf, *wf;
  int fd0, fd1;

  if(argptr(0, (void*)&fd, 2*sizeof(fd[0])) < 0)
    return -1;
  if(pipealloc(&rf, &wf) < 0)
    return -1;
  fd0 = -1;
  if((fd0 = fdalloc(rf)) < 0 || (fd1 = fdalloc(wf)) < 0){
    if(fd0 >= 0)
      myproc()->ofile[fd0] = 0;
    fileclose(rf);
    fileclose(wf);
    return -1;
  }
  fd[0] = fd0;
  fd[1] = fd1;
  return 0;
}
