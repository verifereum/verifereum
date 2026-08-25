Theory vfmTest0441[no_sig_docs]
Ancestors vfmTestDefs0441
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0441_0.nsv", "result0441_1.nsv", "result0441_2.nsv", "result0441_3.nsv", "result0441_4.nsv", "result0441_5.nsv"];
val thyn = "vfmTestDefs0441";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
