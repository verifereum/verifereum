Theory vfmTest2935[no_sig_docs]
Ancestors vfmTestDefs2935
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2935_0.nsv", "result2935_1.nsv", "result2935_2.nsv", "result2935_3.nsv", "result2935_4.nsv", "result2935_5.nsv", "result2935_6.nsv", "result2935_7.nsv", "result2935_8.nsv", "result2935_9.nsv", "result2935_10.nsv", "result2935_11.nsv", "result2935_12.nsv", "result2935_13.nsv", "result2935_14.nsv", "result2935_15.nsv"];
val thyn = "vfmTestDefs2935";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
