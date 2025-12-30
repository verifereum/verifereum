Theory vfmTest0451[no_sig_docs]
Ancestors vfmTestDefs0451
Libs wordsLib vfmTestResultLib
val thyn = "vfmTestDefs0451";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
