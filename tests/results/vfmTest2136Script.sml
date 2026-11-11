Theory vfmTest2136[no_sig_docs]
Ancestors vfmTestDefs2136
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2136_0.nsv", "result2136_1.nsv", "result2136_2.nsv", "result2136_3.nsv", "result2136_4.nsv", "result2136_5.nsv", "result2136_6.nsv", "result2136_7.nsv", "result2136_8.nsv", "result2136_9.nsv", "result2136_10.nsv", "result2136_11.nsv", "result2136_12.nsv", "result2136_13.nsv", "result2136_14.nsv", "result2136_15.nsv", "result2136_16.nsv", "result2136_17.nsv", "result2136_18.nsv", "result2136_19.nsv", "result2136_20.nsv", "result2136_21.nsv", "result2136_22.nsv", "result2136_23.nsv", "result2136_24.nsv", "result2136_25.nsv", "result2136_26.nsv"];
val thyn = "vfmTestDefs2136";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
