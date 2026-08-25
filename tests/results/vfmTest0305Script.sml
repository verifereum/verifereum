Theory vfmTest0305[no_sig_docs]
Ancestors vfmTestDefs0305
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0305_0.nsv", "result0305_1.nsv", "result0305_2.nsv", "result0305_3.nsv"];
val thyn = "vfmTestDefs0305";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
