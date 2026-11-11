Theory vfmTest0060[no_sig_docs]
Ancestors vfmTestDefs0060
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0060_0.nsv", "result0060_1.nsv", "result0060_2.nsv", "result0060_3.nsv", "result0060_4.nsv", "result0060_5.nsv", "result0060_6.nsv", "result0060_7.nsv", "result0060_8.nsv", "result0060_9.nsv"];
val thyn = "vfmTestDefs0060";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
