Theory vfmTest3116[no_sig_docs]
Ancestors vfmTestDefs3116
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3116_0.nsv", "result3116_1.nsv", "result3116_2.nsv", "result3116_3.nsv", "result3116_4.nsv", "result3116_5.nsv", "result3116_6.nsv", "result3116_7.nsv", "result3116_8.nsv", "result3116_9.nsv", "result3116_10.nsv", "result3116_11.nsv", "result3116_12.nsv", "result3116_13.nsv", "result3116_14.nsv", "result3116_15.nsv", "result3116_16.nsv", "result3116_17.nsv", "result3116_18.nsv", "result3116_19.nsv", "result3116_20.nsv", "result3116_21.nsv", "result3116_22.nsv", "result3116_23.nsv", "result3116_24.nsv", "result3116_25.nsv", "result3116_26.nsv", "result3116_27.nsv", "result3116_28.nsv", "result3116_29.nsv"];
val thyn = "vfmTestDefs3116";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
