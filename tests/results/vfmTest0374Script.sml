Theory vfmTest0374[no_sig_docs]
Ancestors vfmTestDefs0374
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0374_0.nsv", "result0374_1.nsv", "result0374_2.nsv", "result0374_3.nsv", "result0374_4.nsv", "result0374_5.nsv", "result0374_6.nsv", "result0374_7.nsv", "result0374_8.nsv", "result0374_9.nsv", "result0374_10.nsv", "result0374_11.nsv", "result0374_12.nsv", "result0374_13.nsv", "result0374_14.nsv", "result0374_15.nsv", "result0374_16.nsv", "result0374_17.nsv", "result0374_18.nsv", "result0374_19.nsv", "result0374_20.nsv", "result0374_21.nsv", "result0374_22.nsv", "result0374_23.nsv", "result0374_24.nsv", "result0374_25.nsv", "result0374_26.nsv", "result0374_27.nsv", "result0374_28.nsv", "result0374_29.nsv", "result0374_30.nsv", "result0374_31.nsv", "result0374_32.nsv", "result0374_33.nsv", "result0374_34.nsv", "result0374_35.nsv", "result0374_36.nsv", "result0374_37.nsv", "result0374_38.nsv", "result0374_39.nsv", "result0374_40.nsv", "result0374_41.nsv", "result0374_42.nsv", "result0374_43.nsv", "result0374_44.nsv", "result0374_45.nsv", "result0374_46.nsv", "result0374_47.nsv", "result0374_48.nsv", "result0374_49.nsv", "result0374_50.nsv", "result0374_51.nsv"];
val thyn = "vfmTestDefs0374";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
