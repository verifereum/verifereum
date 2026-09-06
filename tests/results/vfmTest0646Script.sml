Theory vfmTest0646[no_sig_docs]
Ancestors vfmTestDefs0646
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0646_0.nsv", "result0646_1.nsv", "result0646_2.nsv", "result0646_3.nsv", "result0646_4.nsv", "result0646_5.nsv", "result0646_6.nsv", "result0646_7.nsv", "result0646_8.nsv", "result0646_9.nsv", "result0646_10.nsv", "result0646_11.nsv"];
val thyn = "vfmTestDefs0646";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
