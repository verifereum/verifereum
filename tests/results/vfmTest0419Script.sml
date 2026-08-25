Theory vfmTest0419[no_sig_docs]
Ancestors vfmTestDefs0419
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0419_0.nsv", "result0419_1.nsv", "result0419_2.nsv", "result0419_3.nsv", "result0419_4.nsv", "result0419_5.nsv"];
val thyn = "vfmTestDefs0419";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
