Theory vfmTest3032[no_sig_docs]
Ancestors vfmTestDefs3032
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3032_0.nsv", "result3032_1.nsv", "result3032_2.nsv", "result3032_3.nsv", "result3032_4.nsv", "result3032_5.nsv", "result3032_6.nsv", "result3032_7.nsv", "result3032_8.nsv", "result3032_9.nsv", "result3032_10.nsv", "result3032_11.nsv", "result3032_12.nsv", "result3032_13.nsv", "result3032_14.nsv", "result3032_15.nsv", "result3032_16.nsv", "result3032_17.nsv", "result3032_18.nsv", "result3032_19.nsv", "result3032_20.nsv", "result3032_21.nsv", "result3032_22.nsv", "result3032_23.nsv", "result3032_24.nsv", "result3032_25.nsv", "result3032_26.nsv", "result3032_27.nsv", "result3032_28.nsv", "result3032_29.nsv", "result3032_30.nsv", "result3032_31.nsv", "result3032_32.nsv", "result3032_33.nsv", "result3032_34.nsv"];
val thyn = "vfmTestDefs3032";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
