mylibdir := cat(kernelopts(homedir), kernelopts(dirsep), "maple", kernelopts(dirsep), "toolbox", kernelopts(dirsep), "personal", kernelopts(dirsep), "lib");
FileTools:-MakeDirectory(mylibdir, 'recurse');
LibraryTools:-Create(cat(mylibdir, kernelopts(dirsep), "Biquaternions.mla"));
libname := mylibdir, libname;
restart;
read("Biquaternions.mpl");
savelib( 'Biquaternions' );
