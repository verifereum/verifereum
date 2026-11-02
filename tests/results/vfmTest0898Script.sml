Theory vfmTest0898[no_sig_docs]
Ancestors vfmTestDefs0898
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0898_0.nsv", "result0898_1.nsv", "result0898_2.nsv", "result0898_3.nsv", "result0898_4.nsv", "result0898_5.nsv", "result0898_6.nsv", "result0898_7.nsv", "result0898_8.nsv", "result0898_9.nsv", "result0898_10.nsv", "result0898_11.nsv", "result0898_12.nsv", "result0898_13.nsv", "result0898_14.nsv", "result0898_15.nsv", "result0898_16.nsv", "result0898_17.nsv", "result0898_18.nsv", "result0898_19.nsv", "result0898_20.nsv", "result0898_21.nsv", "result0898_22.nsv", "result0898_23.nsv", "result0898_24.nsv", "result0898_25.nsv", "result0898_26.nsv", "result0898_27.nsv", "result0898_28.nsv", "result0898_29.nsv", "result0898_30.nsv", "result0898_31.nsv", "result0898_32.nsv", "result0898_33.nsv", "result0898_34.nsv", "result0898_35.nsv", "result0898_36.nsv", "result0898_37.nsv", "result0898_38.nsv", "result0898_39.nsv", "result0898_40.nsv", "result0898_41.nsv", "result0898_42.nsv", "result0898_43.nsv", "result0898_44.nsv", "result0898_45.nsv", "result0898_46.nsv"];
val thyn = "vfmTestDefs0898";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
