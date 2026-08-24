Theory vfmTest2675[no_sig_docs]
Ancestors vfmTestDefs2675
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2675_0.nsv", "result2675_1.nsv", "result2675_2.nsv", "result2675_3.nsv"];
val thyn = "vfmTestDefs2675";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
