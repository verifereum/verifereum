Theory vfmTest0819[no_sig_docs]
Ancestors vfmTestDefs0819
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0819";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
