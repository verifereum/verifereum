Theory vfmTest0986[no_sig_docs]
Ancestors vfmTestDefs0986
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0986_0.nsv", "result0986_1.nsv", "result0986_2.nsv", "result0986_3.nsv", "result0986_4.nsv", "result0986_5.nsv"];
val thyn = "vfmTestDefs0986";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
