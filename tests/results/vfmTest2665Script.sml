Theory vfmTest2665[no_sig_docs]
Ancestors vfmTestDefs2665
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2665_0.nsv", "result2665_1.nsv", "result2665_2.nsv", "result2665_3.nsv"];
val thyn = "vfmTestDefs2665";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
