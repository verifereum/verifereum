Theory vfmTest0100[no_sig_docs]
Ancestors vfmTestDefs0100
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0100_0.nsv", "result0100_1.nsv", "result0100_2.nsv", "result0100_3.nsv", "result0100_4.nsv", "result0100_5.nsv"];
val thyn = "vfmTestDefs0100";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
