Theory vfmTest3043[no_sig_docs]
Ancestors vfmTestDefs3043
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3043_0.nsv", "result3043_1.nsv", "result3043_2.nsv", "result3043_3.nsv", "result3043_4.nsv", "result3043_5.nsv", "result3043_6.nsv", "result3043_7.nsv", "result3043_8.nsv", "result3043_9.nsv", "result3043_10.nsv", "result3043_11.nsv", "result3043_12.nsv", "result3043_13.nsv", "result3043_14.nsv", "result3043_15.nsv", "result3043_16.nsv", "result3043_17.nsv", "result3043_18.nsv", "result3043_19.nsv", "result3043_20.nsv", "result3043_21.nsv"];
val thyn = "vfmTestDefs3043";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
