Theory vfmTest0131[no_sig_docs]
Ancestors vfmTestDefs0131
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0131_0.nsv", "result0131_1.nsv", "result0131_2.nsv", "result0131_3.nsv", "result0131_4.nsv", "result0131_5.nsv"];
val thyn = "vfmTestDefs0131";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
