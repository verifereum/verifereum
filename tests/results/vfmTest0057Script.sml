Theory vfmTest0057[no_sig_docs]
Ancestors vfmTestDefs0057
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0057_0.nsv", "result0057_1.nsv"];
val thyn = "vfmTestDefs0057";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
