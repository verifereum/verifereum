Theory vfmTest0723[no_sig_docs]
Ancestors vfmTestDefs0723
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0723_0.nsv", "result0723_1.nsv", "result0723_2.nsv", "result0723_3.nsv", "result0723_4.nsv", "result0723_5.nsv", "result0723_6.nsv", "result0723_7.nsv", "result0723_8.nsv", "result0723_9.nsv", "result0723_10.nsv", "result0723_11.nsv", "result0723_12.nsv", "result0723_13.nsv", "result0723_14.nsv", "result0723_15.nsv", "result0723_16.nsv", "result0723_17.nsv", "result0723_18.nsv", "result0723_19.nsv", "result0723_20.nsv", "result0723_21.nsv", "result0723_22.nsv", "result0723_23.nsv", "result0723_24.nsv", "result0723_25.nsv", "result0723_26.nsv", "result0723_27.nsv", "result0723_28.nsv", "result0723_29.nsv", "result0723_30.nsv", "result0723_31.nsv", "result0723_32.nsv", "result0723_33.nsv", "result0723_34.nsv", "result0723_35.nsv", "result0723_36.nsv", "result0723_37.nsv", "result0723_38.nsv", "result0723_39.nsv", "result0723_40.nsv", "result0723_41.nsv", "result0723_42.nsv", "result0723_43.nsv", "result0723_44.nsv", "result0723_45.nsv", "result0723_46.nsv", "result0723_47.nsv", "result0723_48.nsv", "result0723_49.nsv", "result0723_50.nsv", "result0723_51.nsv", "result0723_52.nsv", "result0723_53.nsv", "result0723_54.nsv"];
val thyn = "vfmTestDefs0723";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
