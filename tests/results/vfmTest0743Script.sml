Theory vfmTest0743[no_sig_docs]
Ancestors vfmTestDefs0743
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0743_0.nsv", "result0743_1.nsv", "result0743_2.nsv", "result0743_3.nsv", "result0743_4.nsv", "result0743_5.nsv", "result0743_6.nsv", "result0743_7.nsv", "result0743_8.nsv", "result0743_9.nsv", "result0743_10.nsv", "result0743_11.nsv"];
val thyn = "vfmTestDefs0743";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
