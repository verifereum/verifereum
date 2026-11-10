Theory vfmTest3060[no_sig_docs]
Ancestors vfmTestDefs3060
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3060_0.nsv", "result3060_1.nsv", "result3060_2.nsv", "result3060_3.nsv", "result3060_4.nsv", "result3060_5.nsv", "result3060_6.nsv", "result3060_7.nsv", "result3060_8.nsv", "result3060_9.nsv", "result3060_10.nsv", "result3060_11.nsv", "result3060_12.nsv", "result3060_13.nsv", "result3060_14.nsv", "result3060_15.nsv", "result3060_16.nsv", "result3060_17.nsv", "result3060_18.nsv", "result3060_19.nsv", "result3060_20.nsv", "result3060_21.nsv", "result3060_22.nsv", "result3060_23.nsv", "result3060_24.nsv"];
val thyn = "vfmTestDefs3060";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
