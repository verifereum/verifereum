Theory vfmTest0097[no_sig_docs]
Ancestors vfmTestDefs0097
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0097_0.nsv", "result0097_1.nsv", "result0097_2.nsv", "result0097_3.nsv", "result0097_4.nsv", "result0097_5.nsv", "result0097_6.nsv", "result0097_7.nsv", "result0097_8.nsv", "result0097_9.nsv", "result0097_10.nsv", "result0097_11.nsv", "result0097_12.nsv", "result0097_13.nsv", "result0097_14.nsv", "result0097_15.nsv"];
val thyn = "vfmTestDefs0097";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
