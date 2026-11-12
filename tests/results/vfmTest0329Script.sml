Theory vfmTest0329[no_sig_docs]
Ancestors vfmTestDefs0329
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0329_0.nsv", "result0329_1.nsv", "result0329_2.nsv", "result0329_3.nsv", "result0329_4.nsv", "result0329_5.nsv", "result0329_6.nsv", "result0329_7.nsv", "result0329_8.nsv", "result0329_9.nsv", "result0329_10.nsv", "result0329_11.nsv", "result0329_12.nsv", "result0329_13.nsv", "result0329_14.nsv", "result0329_15.nsv", "result0329_16.nsv", "result0329_17.nsv", "result0329_18.nsv", "result0329_19.nsv", "result0329_20.nsv", "result0329_21.nsv", "result0329_22.nsv", "result0329_23.nsv", "result0329_24.nsv", "result0329_25.nsv", "result0329_26.nsv", "result0329_27.nsv", "result0329_28.nsv", "result0329_29.nsv", "result0329_30.nsv", "result0329_31.nsv", "result0329_32.nsv", "result0329_33.nsv", "result0329_34.nsv", "result0329_35.nsv", "result0329_36.nsv", "result0329_37.nsv", "result0329_38.nsv", "result0329_39.nsv", "result0329_40.nsv", "result0329_41.nsv", "result0329_42.nsv", "result0329_43.nsv", "result0329_44.nsv", "result0329_45.nsv", "result0329_46.nsv", "result0329_47.nsv", "result0329_48.nsv", "result0329_49.nsv", "result0329_50.nsv", "result0329_51.nsv", "result0329_52.nsv", "result0329_53.nsv", "result0329_54.nsv", "result0329_55.nsv"];
val thyn = "vfmTestDefs0329";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
