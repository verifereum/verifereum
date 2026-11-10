Theory vfmTest3066[no_sig_docs]
Ancestors vfmTestDefs3066
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3066_0.nsv", "result3066_1.nsv", "result3066_2.nsv", "result3066_3.nsv", "result3066_4.nsv", "result3066_5.nsv", "result3066_6.nsv", "result3066_7.nsv", "result3066_8.nsv", "result3066_9.nsv", "result3066_10.nsv", "result3066_11.nsv", "result3066_12.nsv", "result3066_13.nsv", "result3066_14.nsv", "result3066_15.nsv", "result3066_16.nsv", "result3066_17.nsv", "result3066_18.nsv", "result3066_19.nsv", "result3066_20.nsv", "result3066_21.nsv", "result3066_22.nsv", "result3066_23.nsv", "result3066_24.nsv", "result3066_25.nsv", "result3066_26.nsv", "result3066_27.nsv", "result3066_28.nsv", "result3066_29.nsv", "result3066_30.nsv", "result3066_31.nsv", "result3066_32.nsv"];
val thyn = "vfmTestDefs3066";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
