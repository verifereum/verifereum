Theory vfmTest3000[no_sig_docs]
Ancestors vfmTestDefs3000
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3000_0.nsv", "result3000_1.nsv", "result3000_2.nsv", "result3000_3.nsv", "result3000_4.nsv", "result3000_5.nsv", "result3000_6.nsv", "result3000_7.nsv", "result3000_8.nsv", "result3000_9.nsv", "result3000_10.nsv", "result3000_11.nsv", "result3000_12.nsv", "result3000_13.nsv", "result3000_14.nsv", "result3000_15.nsv", "result3000_16.nsv", "result3000_17.nsv", "result3000_18.nsv", "result3000_19.nsv", "result3000_20.nsv", "result3000_21.nsv", "result3000_22.nsv", "result3000_23.nsv"];
val thyn = "vfmTestDefs3000";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
