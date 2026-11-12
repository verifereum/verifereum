Theory vfmTest0116[no_sig_docs]
Ancestors vfmTestDefs0116
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0116_0.nsv", "result0116_1.nsv", "result0116_2.nsv", "result0116_3.nsv", "result0116_4.nsv", "result0116_5.nsv", "result0116_6.nsv", "result0116_7.nsv", "result0116_8.nsv", "result0116_9.nsv", "result0116_10.nsv", "result0116_11.nsv", "result0116_12.nsv", "result0116_13.nsv", "result0116_14.nsv", "result0116_15.nsv", "result0116_16.nsv", "result0116_17.nsv", "result0116_18.nsv", "result0116_19.nsv", "result0116_20.nsv", "result0116_21.nsv", "result0116_22.nsv", "result0116_23.nsv", "result0116_24.nsv", "result0116_25.nsv", "result0116_26.nsv", "result0116_27.nsv", "result0116_28.nsv", "result0116_29.nsv", "result0116_30.nsv", "result0116_31.nsv", "result0116_32.nsv", "result0116_33.nsv", "result0116_34.nsv", "result0116_35.nsv", "result0116_36.nsv", "result0116_37.nsv", "result0116_38.nsv", "result0116_39.nsv"];
val thyn = "vfmTestDefs0116";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
