Theory vfmTest2481[no_sig_docs]
Ancestors vfmTestDefs2481
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2481_0.nsv", "result2481_1.nsv", "result2481_2.nsv", "result2481_3.nsv", "result2481_4.nsv", "result2481_5.nsv", "result2481_6.nsv", "result2481_7.nsv", "result2481_8.nsv", "result2481_9.nsv", "result2481_10.nsv", "result2481_11.nsv", "result2481_12.nsv", "result2481_13.nsv", "result2481_14.nsv", "result2481_15.nsv"];
val thyn = "vfmTestDefs2481";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
