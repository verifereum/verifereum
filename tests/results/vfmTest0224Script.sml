Theory vfmTest0224[no_sig_docs]
Ancestors vfmTestDefs0224
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0224_0.nsv", "result0224_1.nsv", "result0224_2.nsv", "result0224_3.nsv", "result0224_4.nsv", "result0224_5.nsv", "result0224_6.nsv", "result0224_7.nsv", "result0224_8.nsv", "result0224_9.nsv", "result0224_10.nsv", "result0224_11.nsv", "result0224_12.nsv", "result0224_13.nsv", "result0224_14.nsv", "result0224_15.nsv", "result0224_16.nsv", "result0224_17.nsv", "result0224_18.nsv", "result0224_19.nsv", "result0224_20.nsv", "result0224_21.nsv", "result0224_22.nsv", "result0224_23.nsv", "result0224_24.nsv", "result0224_25.nsv", "result0224_26.nsv", "result0224_27.nsv", "result0224_28.nsv", "result0224_29.nsv", "result0224_30.nsv", "result0224_31.nsv", "result0224_32.nsv", "result0224_33.nsv", "result0224_34.nsv", "result0224_35.nsv", "result0224_36.nsv", "result0224_37.nsv", "result0224_38.nsv", "result0224_39.nsv", "result0224_40.nsv", "result0224_41.nsv", "result0224_42.nsv", "result0224_43.nsv", "result0224_44.nsv", "result0224_45.nsv"];
val thyn = "vfmTestDefs0224";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
