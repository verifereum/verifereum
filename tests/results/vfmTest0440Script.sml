Theory vfmTest0440[no_sig_docs]
Ancestors vfmTestDefs0440
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0440_0.nsv", "result0440_1.nsv", "result0440_2.nsv", "result0440_3.nsv", "result0440_4.nsv", "result0440_5.nsv", "result0440_6.nsv", "result0440_7.nsv", "result0440_8.nsv", "result0440_9.nsv", "result0440_10.nsv", "result0440_11.nsv", "result0440_12.nsv", "result0440_13.nsv", "result0440_14.nsv", "result0440_15.nsv", "result0440_16.nsv", "result0440_17.nsv", "result0440_18.nsv", "result0440_19.nsv", "result0440_20.nsv", "result0440_21.nsv", "result0440_22.nsv", "result0440_23.nsv", "result0440_24.nsv", "result0440_25.nsv", "result0440_26.nsv"];
val thyn = "vfmTestDefs0440";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
