Theory vfmTest0179[no_sig_docs]
Ancestors vfmTestDefs0179
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0179_0.nsv", "result0179_1.nsv", "result0179_2.nsv", "result0179_3.nsv", "result0179_4.nsv", "result0179_5.nsv", "result0179_6.nsv", "result0179_7.nsv", "result0179_8.nsv", "result0179_9.nsv", "result0179_10.nsv", "result0179_11.nsv", "result0179_12.nsv", "result0179_13.nsv", "result0179_14.nsv", "result0179_15.nsv", "result0179_16.nsv", "result0179_17.nsv", "result0179_18.nsv", "result0179_19.nsv", "result0179_20.nsv", "result0179_21.nsv", "result0179_22.nsv", "result0179_23.nsv", "result0179_24.nsv", "result0179_25.nsv", "result0179_26.nsv", "result0179_27.nsv", "result0179_28.nsv", "result0179_29.nsv", "result0179_30.nsv", "result0179_31.nsv", "result0179_32.nsv", "result0179_33.nsv", "result0179_34.nsv", "result0179_35.nsv", "result0179_36.nsv", "result0179_37.nsv", "result0179_38.nsv", "result0179_39.nsv", "result0179_40.nsv", "result0179_41.nsv", "result0179_42.nsv", "result0179_43.nsv", "result0179_44.nsv", "result0179_45.nsv", "result0179_46.nsv", "result0179_47.nsv"];
val thyn = "vfmTestDefs0179";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
