Theory vfmTest0053[no_sig_docs]
Ancestors vfmTestDefs0053
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0053_0.nsv", "result0053_1.nsv", "result0053_2.nsv", "result0053_3.nsv", "result0053_4.nsv", "result0053_5.nsv", "result0053_6.nsv", "result0053_7.nsv", "result0053_8.nsv", "result0053_9.nsv", "result0053_10.nsv", "result0053_11.nsv"];
val thyn = "vfmTestDefs0053";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
