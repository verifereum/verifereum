Theory vfmTest2013[no_sig_docs]
Ancestors vfmTestDefs2013
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2013_0.nsv"];
val thyn = "vfmTestDefs2013";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
