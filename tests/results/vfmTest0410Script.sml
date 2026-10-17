Theory vfmTest0410[no_sig_docs]
Ancestors vfmTestDefs0410
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0410_0.nsv", "result0410_1.nsv", "result0410_2.nsv", "result0410_3.nsv", "result0410_4.nsv", "result0410_5.nsv"];
val thyn = "vfmTestDefs0410";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
