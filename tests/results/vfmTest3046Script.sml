Theory vfmTest3046[no_sig_docs]
Ancestors vfmTestDefs3046
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3046_0.nsv", "result3046_1.nsv", "result3046_2.nsv", "result3046_3.nsv", "result3046_4.nsv", "result3046_5.nsv", "result3046_6.nsv", "result3046_7.nsv", "result3046_8.nsv", "result3046_9.nsv", "result3046_10.nsv", "result3046_11.nsv", "result3046_12.nsv", "result3046_13.nsv", "result3046_14.nsv", "result3046_15.nsv", "result3046_16.nsv", "result3046_17.nsv", "result3046_18.nsv", "result3046_19.nsv", "result3046_20.nsv", "result3046_21.nsv", "result3046_22.nsv", "result3046_23.nsv"];
val thyn = "vfmTestDefs3046";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
