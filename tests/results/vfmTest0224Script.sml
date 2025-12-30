Theory vfmTest0224[no_sig_docs]
Ancestors vfmTestDefs0224
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0224";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
