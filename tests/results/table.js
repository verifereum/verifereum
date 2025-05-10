<script type="text/javascript">
  const label = document.createElement('label')
  const span = document.createElement('span')
  span.textContent = ' hide passed'
  const checkbox = document.createElement('input')
  checkbox.type = 'checkbox'
  checkbox.addEventListener('change', (e) => {
    if (e.currentTarget.checked) {
      document.querySelectorAll('tr:has(.pass)').forEach((tr) =>
        tr.classList.add('hide'))
    } else {
      document.querySelectorAll('tr:has(.pass)').forEach((tr) =>
        tr.classList.remove('hide'))
    }
  })
  label.append(checkbox, span)
  document.addEventListener('DOMContentLoaded', () =>
    document.querySelector('body').insertBefore(
      label, document.querySelector('table')))
</script>
