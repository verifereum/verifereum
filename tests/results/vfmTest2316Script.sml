Theory vfmTest2316[no_sig_docs]
Ancestors vfmTestDefs2316
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2316_0.nsv", "result2316_1.nsv", "result2316_2.nsv", "result2316_3.nsv", "result2316_4.nsv", "result2316_5.nsv", "result2316_6.nsv", "result2316_7.nsv", "result2316_8.nsv", "result2316_9.nsv", "result2316_10.nsv", "result2316_11.nsv", "result2316_12.nsv", "result2316_13.nsv", "result2316_14.nsv", "result2316_15.nsv", "result2316_16.nsv", "result2316_17.nsv", "result2316_18.nsv", "result2316_19.nsv", "result2316_20.nsv", "result2316_21.nsv", "result2316_22.nsv", "result2316_23.nsv"];
val thyn = "vfmTestDefs2316";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
