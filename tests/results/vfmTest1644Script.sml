Theory vfmTest1644[no_sig_docs]
Ancestors vfmTestDefs1644
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1644_0.nsv", "result1644_1.nsv", "result1644_2.nsv", "result1644_3.nsv", "result1644_4.nsv", "result1644_5.nsv", "result1644_6.nsv", "result1644_7.nsv"];
val thyn = "vfmTestDefs1644";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
