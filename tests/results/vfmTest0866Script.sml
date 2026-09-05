Theory vfmTest0866[no_sig_docs]
Ancestors vfmTestDefs0866
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0866_0.nsv", "result0866_1.nsv"];
val thyn = "vfmTestDefs0866";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
