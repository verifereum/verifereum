Theory vfmTest0272[no_sig_docs]
Ancestors vfmTestDefs0272
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0272_0.nsv", "result0272_1.nsv", "result0272_2.nsv", "result0272_3.nsv"];
val thyn = "vfmTestDefs0272";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
