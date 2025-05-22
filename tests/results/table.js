const mk_label = (hidecls) => {
  const label = document.createElement('label')
  const span = document.createElement('span')
  span.textContent = ` hide ${hidecls}`
  const selector = `tr:has(.${hidecls})`
  const checkbox = document.createElement('input')
  checkbox.type = 'checkbox'
  checkbox.addEventListener('change', (e) => {
    if (e.currentTarget.checked) {
      document.querySelectorAll(selector).forEach((tr) => {
        tr.classList.add(`hchk-${hidecls}`)
        tr.classList.add('hide')
      })
    } else {
      document.querySelectorAll(selector).forEach((tr) => {
        tr.classList.remove(`hchk-${hidecls}`)
        if (!tr.classList.toString().includes('hchk-'))
          tr.classList.remove('hide')
      })
    }
  })
  label.append(checkbox, span)
  return label
}

const div = document.createElement('div')
div.append(mk_label('passed'),
           mk_label('timeout'),
           mk_label('precompile'))

document.addEventListener('DOMContentLoaded', () =>
  document.querySelector('body').insertBefore(
    div, document.querySelector('table')))
