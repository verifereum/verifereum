Theory vfmTest2833[no_sig_docs]
Ancestors vfmTestDefs2833
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2833_0.nsv", "result2833_1.nsv", "result2833_2.nsv", "result2833_3.nsv"];
val thyn = "vfmTestDefs2833";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
