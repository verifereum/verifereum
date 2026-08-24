Theory vfmTest2106[no_sig_docs]
Ancestors vfmTestDefs2106
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs [];
val thyn = "vfmTestDefs2106";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
