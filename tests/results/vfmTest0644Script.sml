Theory vfmTest0644[no_sig_docs]
Ancestors vfmTestDefs0644
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0644_0.nsv", "result0644_1.nsv", "result0644_2.nsv", "result0644_3.nsv", "result0644_4.nsv", "result0644_5.nsv", "result0644_6.nsv", "result0644_7.nsv"];
val thyn = "vfmTestDefs0644";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
