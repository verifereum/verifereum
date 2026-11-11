Theory vfmTest0086[no_sig_docs]
Ancestors vfmTestDefs0086
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0086_0.nsv", "result0086_1.nsv", "result0086_2.nsv", "result0086_3.nsv", "result0086_4.nsv", "result0086_5.nsv", "result0086_6.nsv", "result0086_7.nsv", "result0086_8.nsv", "result0086_9.nsv", "result0086_10.nsv", "result0086_11.nsv", "result0086_12.nsv", "result0086_13.nsv", "result0086_14.nsv", "result0086_15.nsv", "result0086_16.nsv", "result0086_17.nsv", "result0086_18.nsv", "result0086_19.nsv", "result0086_20.nsv", "result0086_21.nsv", "result0086_22.nsv", "result0086_23.nsv", "result0086_24.nsv", "result0086_25.nsv", "result0086_26.nsv", "result0086_27.nsv", "result0086_28.nsv", "result0086_29.nsv", "result0086_30.nsv", "result0086_31.nsv", "result0086_32.nsv", "result0086_33.nsv", "result0086_34.nsv"];
val thyn = "vfmTestDefs0086";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
