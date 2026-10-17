Theory vfmTest0225[no_sig_docs]
Ancestors vfmTestDefs0225
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0225_0.nsv", "result0225_1.nsv", "result0225_2.nsv", "result0225_3.nsv", "result0225_4.nsv", "result0225_5.nsv", "result0225_6.nsv", "result0225_7.nsv", "result0225_8.nsv", "result0225_9.nsv", "result0225_10.nsv", "result0225_11.nsv", "result0225_12.nsv", "result0225_13.nsv", "result0225_14.nsv", "result0225_15.nsv", "result0225_16.nsv", "result0225_17.nsv", "result0225_18.nsv", "result0225_19.nsv", "result0225_20.nsv", "result0225_21.nsv", "result0225_22.nsv", "result0225_23.nsv", "result0225_24.nsv", "result0225_25.nsv", "result0225_26.nsv", "result0225_27.nsv", "result0225_28.nsv", "result0225_29.nsv", "result0225_30.nsv", "result0225_31.nsv", "result0225_32.nsv", "result0225_33.nsv"];
val thyn = "vfmTestDefs0225";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
