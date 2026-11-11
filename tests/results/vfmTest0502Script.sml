Theory vfmTest0502[no_sig_docs]
Ancestors vfmTestDefs0502
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0502_0.nsv", "result0502_1.nsv", "result0502_2.nsv", "result0502_3.nsv", "result0502_4.nsv", "result0502_5.nsv", "result0502_6.nsv", "result0502_7.nsv", "result0502_8.nsv", "result0502_9.nsv", "result0502_10.nsv", "result0502_11.nsv"];
val thyn = "vfmTestDefs0502";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
