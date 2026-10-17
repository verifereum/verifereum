Theory vfmTest2354[no_sig_docs]
Ancestors vfmTestDefs2354
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2354_0.nsv", "result2354_1.nsv", "result2354_2.nsv", "result2354_3.nsv", "result2354_4.nsv", "result2354_5.nsv", "result2354_6.nsv", "result2354_7.nsv"];
val thyn = "vfmTestDefs2354";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
