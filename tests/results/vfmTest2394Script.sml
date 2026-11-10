Theory vfmTest2394[no_sig_docs]
Ancestors vfmTestDefs2394
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2394_0.nsv", "result2394_1.nsv", "result2394_2.nsv", "result2394_3.nsv", "result2394_4.nsv", "result2394_5.nsv", "result2394_6.nsv", "result2394_7.nsv", "result2394_8.nsv", "result2394_9.nsv", "result2394_10.nsv", "result2394_11.nsv", "result2394_12.nsv", "result2394_13.nsv", "result2394_14.nsv", "result2394_15.nsv", "result2394_16.nsv", "result2394_17.nsv", "result2394_18.nsv", "result2394_19.nsv"];
val thyn = "vfmTestDefs2394";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
