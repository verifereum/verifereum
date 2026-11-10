Theory vfmTest0977[no_sig_docs]
Ancestors vfmTestDefs0977
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0977_0.nsv", "result0977_1.nsv", "result0977_2.nsv", "result0977_3.nsv", "result0977_4.nsv", "result0977_5.nsv", "result0977_6.nsv", "result0977_7.nsv", "result0977_8.nsv", "result0977_9.nsv", "result0977_10.nsv", "result0977_11.nsv", "result0977_12.nsv", "result0977_13.nsv", "result0977_14.nsv", "result0977_15.nsv", "result0977_16.nsv", "result0977_17.nsv", "result0977_18.nsv", "result0977_19.nsv", "result0977_20.nsv", "result0977_21.nsv", "result0977_22.nsv", "result0977_23.nsv"];
val thyn = "vfmTestDefs0977";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
