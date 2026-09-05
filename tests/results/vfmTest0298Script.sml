Theory vfmTest0298[no_sig_docs]
Ancestors vfmTestDefs0298
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0298_0.nsv", "result0298_1.nsv", "result0298_2.nsv", "result0298_3.nsv", "result0298_4.nsv", "result0298_5.nsv", "result0298_6.nsv", "result0298_7.nsv", "result0298_8.nsv", "result0298_9.nsv", "result0298_10.nsv", "result0298_11.nsv", "result0298_12.nsv", "result0298_13.nsv", "result0298_14.nsv", "result0298_15.nsv", "result0298_16.nsv", "result0298_17.nsv", "result0298_18.nsv", "result0298_19.nsv", "result0298_20.nsv", "result0298_21.nsv", "result0298_22.nsv", "result0298_23.nsv", "result0298_24.nsv", "result0298_25.nsv", "result0298_26.nsv", "result0298_27.nsv", "result0298_28.nsv", "result0298_29.nsv", "result0298_30.nsv", "result0298_31.nsv", "result0298_32.nsv", "result0298_33.nsv", "result0298_34.nsv", "result0298_35.nsv", "result0298_36.nsv", "result0298_37.nsv", "result0298_38.nsv", "result0298_39.nsv", "result0298_40.nsv", "result0298_41.nsv", "result0298_42.nsv", "result0298_43.nsv", "result0298_44.nsv", "result0298_45.nsv", "result0298_46.nsv", "result0298_47.nsv", "result0298_48.nsv", "result0298_49.nsv", "result0298_50.nsv", "result0298_51.nsv", "result0298_52.nsv", "result0298_53.nsv", "result0298_54.nsv", "result0298_55.nsv", "result0298_56.nsv", "result0298_57.nsv", "result0298_58.nsv", "result0298_59.nsv", "result0298_60.nsv", "result0298_61.nsv"];
val thyn = "vfmTestDefs0298";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
