Theory vfmTest2094[no_sig_docs]
Ancestors vfmTestDefs2094
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2094_0.nsv"];
val thyn = "vfmTestDefs2094";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
