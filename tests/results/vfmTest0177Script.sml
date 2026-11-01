Theory vfmTest0177[no_sig_docs]
Ancestors vfmTestDefs0177
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0177_0.nsv", "result0177_1.nsv", "result0177_2.nsv", "result0177_3.nsv", "result0177_4.nsv", "result0177_5.nsv", "result0177_6.nsv", "result0177_7.nsv"];
val thyn = "vfmTestDefs0177";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
