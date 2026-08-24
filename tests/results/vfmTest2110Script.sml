Theory vfmTest2110[no_sig_docs]
Ancestors vfmTestDefs2110
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs [];
val thyn = "vfmTestDefs2110";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
