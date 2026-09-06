Theory vfmTest0035[no_sig_docs]
Ancestors vfmTestDefs0035
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0035_0.nsv", "result0035_1.nsv", "result0035_2.nsv", "result0035_3.nsv", "result0035_4.nsv", "result0035_5.nsv", "result0035_6.nsv", "result0035_7.nsv", "result0035_8.nsv", "result0035_9.nsv", "result0035_10.nsv", "result0035_11.nsv", "result0035_12.nsv", "result0035_13.nsv", "result0035_14.nsv", "result0035_15.nsv", "result0035_16.nsv", "result0035_17.nsv", "result0035_18.nsv", "result0035_19.nsv", "result0035_20.nsv", "result0035_21.nsv", "result0035_22.nsv", "result0035_23.nsv", "result0035_24.nsv", "result0035_25.nsv", "result0035_26.nsv", "result0035_27.nsv", "result0035_28.nsv", "result0035_29.nsv", "result0035_30.nsv", "result0035_31.nsv", "result0035_32.nsv", "result0035_33.nsv", "result0035_34.nsv", "result0035_35.nsv"];
val thyn = "vfmTestDefs0035";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
