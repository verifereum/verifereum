Theory vfmTest0692[no_sig_docs]
Ancestors vfmTestDefs0692
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0692_0.nsv", "result0692_1.nsv", "result0692_2.nsv", "result0692_3.nsv", "result0692_4.nsv", "result0692_5.nsv"];
val thyn = "vfmTestDefs0692";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
