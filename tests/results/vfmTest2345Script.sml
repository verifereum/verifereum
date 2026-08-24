Theory vfmTest2345[no_sig_docs]
Ancestors vfmTestDefs2345
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2345_0.nsv"];
val thyn = "vfmTestDefs2345";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
