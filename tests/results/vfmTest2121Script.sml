Theory vfmTest2121[no_sig_docs]
Ancestors vfmTestDefs2121
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2121_0.nsv", "result2121_1.nsv", "result2121_2.nsv", "result2121_3.nsv", "result2121_4.nsv", "result2121_5.nsv", "result2121_6.nsv", "result2121_7.nsv", "result2121_8.nsv", "result2121_9.nsv", "result2121_10.nsv", "result2121_11.nsv", "result2121_12.nsv", "result2121_13.nsv", "result2121_14.nsv", "result2121_15.nsv", "result2121_16.nsv", "result2121_17.nsv", "result2121_18.nsv", "result2121_19.nsv", "result2121_20.nsv", "result2121_21.nsv", "result2121_22.nsv", "result2121_23.nsv", "result2121_24.nsv", "result2121_25.nsv"];
val thyn = "vfmTestDefs2121";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
